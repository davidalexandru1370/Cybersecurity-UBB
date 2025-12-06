package com.example.backend.core.domain;

import com.example.backend.core.enums.Role;

import jakarta.persistence.Column;
import jakarta.persistence.Entity;
import jakarta.persistence.GeneratedValue;
import jakarta.persistence.GenerationType;
import jakarta.persistence.Id;
import jakarta.persistence.SequenceGenerator;
import jakarta.persistence.Table;

@Entity
@Table(name = "user")
public class User {
    @Id
    @GeneratedValue(strategy = GenerationType.SEQUENCE, generator = "user_id_gen")
    @SequenceGenerator(name = "user_id_gen", sequenceName = "user_id_seq")
    @Column(name = "id", nullable = false)
    private Long id;

    @Column(name = "title", nullable = false, length = 200)
    private String email;

    @Column(name = "password", nullable = false, length = 200)
    private String password;

    @Column(name = "role", nullable = false, length = 50)
    private String role;

    public User(String email, String password, Role role) {
        this.email = email;
        this.password = password;
        this.role = role.name();
    }

    public Long getId() {
        return id;
    }

    public String getUsername() {
        return email;
    }

    public String getPassword() {
        return password;
    }

    public String getRole() {
        return role;
    }
}
