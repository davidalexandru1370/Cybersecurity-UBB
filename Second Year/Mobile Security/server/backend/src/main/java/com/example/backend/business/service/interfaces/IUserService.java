package com.example.backend.business.service.interfaces;

import com.example.backend.business.entities.CreateUserDTO;
import com.example.backend.core.domain.User;
import com.example.backend.core.exceptions.ExistingAccountException;
import com.example.backend.core.exceptions.ExpiredTokenException;

public interface IUserService {
    User createUser(CreateUserDTO createUserDTO) throws ExistingAccountException;

    User getUserByEmail(String email);

    boolean validateUserCredentials(String email, String password);

    String generateAuthToken(String email, Long id);

    Boolean validateAuthToken(String token) throws ExpiredTokenException;
}
