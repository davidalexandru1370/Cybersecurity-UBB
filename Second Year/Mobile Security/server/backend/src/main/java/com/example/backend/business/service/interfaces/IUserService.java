package com.example.backend.business.service.interfaces;

import com.example.backend.business.entities.CreateUserDTO;
import com.example.backend.core.domain.User;
import com.example.backend.core.exceptions.ExistingAccountException;
import com.example.backend.core.exceptions.ExpiredTokenException;
import com.example.backend.core.exceptions.NotFoundException;

public interface IUserService {
    User createUser(CreateUserDTO createUserDTO) throws ExistingAccountException;

    User getUserByEmail(String email);

    User getUserById(String id) throws NotFoundException;

    boolean validateUserCredentials(String email, String password);

    String generateAuthToken(String email, Long id);

    Boolean validateAuthToken(String token) throws ExpiredTokenException;
}
